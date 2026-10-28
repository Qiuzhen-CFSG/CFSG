module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.Construction
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd.Sylow
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd
public import Theory.Representation.BinaryOffender.Stability

/-!
# Stable offender families on the ordinary seven-letter module

Every nonempty stable family on the binary natural S₇-module contains each
transposition subgroup. Indeed, classification supplies a conjugate of A_m;
the absence of strong offenders makes its transposition subgroup have the
same weight. Stability and conjugacy then supply all transpositions. In a
Sylow two-group containing D, all offenders lie in D and its three generators
belong to the family, so the family generates exactly D.

This is the concrete B.3.2(4)/B.2.9(1) calculation used in 13.6.22, printed
p.932 of Aschbacher–Smith, combined manuscript of 1 March 2004. Identifying
the family from the actual W_K action is a separate source obligation.
-/
@[expose] public section
open Subgroup Equiv Equiv.Perm
open CFSG.Quasithin.ChapterB.Offenders Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking


/-- The two source notations use the same three literal pair swaps. -/
theorem D_eq_threeTranspositions : D 7 = threeTranspositions := by
  unfold D disjointTranspositions threeTranspositions
  congr 1
  ext g
  constructor
  · rintro ⟨i, _, rfl⟩
    fin_cases i <;> simp [pairSwap]
  · intro hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨2, by decide, rfl⟩

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
    (hA : IsBestOffender (BinaryPermutation.naturalRepresentation (Fin 7)) A) :
    weight (BinaryPermutation.naturalRepresentation (Fin 7)) A = Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 7)) := by
  have hd := fixedCodim_add_finrank (BinaryPermutation.naturalRepresentation (Fin 7)) A
  have hl := (hA.isOffender (BinaryPermutation.naturalRepresentation (Fin 7))).2
  have hu : rank A ≤ fixedCodim (BinaryPermutation.naturalRepresentation (Fin 7)) A := by
    by_contra! h
    exact Odd.not_isStrongOffender_natural (Or.inr rfl) A ⟨hA.1, h⟩
  unfold weight
  omega

/-- An odd-degree natural-module offender contains an odd permutation. -/
theorem offender_not_le_alternating (A : Subgroup (Perm (Fin 7)))
    (hA : IsBestOffender (BinaryPermutation.naturalRepresentation (Fin 7)) A) :
    ¬ A ≤ alternatingGroup (Fin 7) := by
  obtain ⟨m, hm, _, g, rfl⟩ :=
    (Odd.isBestOffender_natural_iff_caseAFamily (Or.inr rfl) A).mp hA
  intro he
  have ht := he (mem_map.mpr ⟨pairSwap 7 0, pairSwap_mem 0 (by change 0 < m; omega), rfl⟩)
  rw [Equiv.Perm.mem_alternatingGroup] at ht
  norm_num [pairSwap, MulAut.conj_apply, map_mul, map_inv, mul_comm, mul_left_comm] at ht

/-- The actual image is S₇ once it contains A₇ and a natural-module offender. -/
theorem eq_top_of_alternating_le_of_offender (H A : Subgroup (Perm (Fin 7)))
    (hH : alternatingGroup (Fin 7) ≤ H)
    (hA : IsBestOffender (BinaryPermutation.naturalRepresentation (Fin 7)) A)
    (hAH : A ≤ H) : H = ⊤ := by
  have hd : H.index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le hH
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h | h
  · exact index_eq_one.mp h
  · exact (offender_not_le_alternating A hA
      ((Equiv.Perm.eq_alternatingGroup_of_index_eq_two h) ▸ hAH)).elim

/-- Stability and the absence of strong offenders close this family downward
among the actual natural-module offenders. -/
theorem stable_downward {P : Set (Subgroup (Perm (Fin 7)))}
    (hP : IsStable (BinaryPermutation.naturalRepresentation (Fin 7)) P) {A B : Subgroup (Perm (Fin 7))}
    (hA : A ∈ P) (hB : IsBestOffender (BinaryPermutation.naturalRepresentation (Fin 7)) B) (hBA : B ≤ A) : B ∈ P := by
  apply hP.2.2.2 A hA B hB.1
  exact ⟨hBA, (offender_weight B hB).trans (offender_weight A (hP.2.1 A hA)).symm⟩

/-- Every transposition subgroup belongs to every nonempty stable family. -/
theorem transposition_mem_stable {P : Set (Subgroup (Perm (Fin 7)))}
    (hP : IsStable (BinaryPermutation.naturalRepresentation (Fin 7)) P) (a b : Fin 7) (hab : a ≠ b) :
    zpowers (swap a b) ∈ P := by
  obtain ⟨A, hA⟩ := hP.1
  obtain ⟨m, hm, hm7, g, hg⟩ :=
    (Odd.isBestOffender_natural_iff_caseAFamily (Or.inr rfl) A).mp (hP.2.1 A hA)
  have hsmall : (disjointTranspositions 7 1).map (MulAut.conj g).toMonoidHom ∈ P := by
    apply stable_downward hP hA
      ((Odd.isBestOffender_disjointTranspositions (n := 7) (m := 1) (Or.inr rfl) (by decide) (by decide)).2.2.2.map_conj
        (BinaryPermutation.naturalRepresentation (Fin 7)) g)
    rw [hg]
    exact map_mono (disjointTranspositions_mono hm)
  have hfirst := hP.2.2.1 _ hsmall g⁻¹
  rw [show ((disjointTranspositions 7 1).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = disjointTranspositions 7 1 from by
    change ((disjointTranspositions 7 1).conjBy g).conjBy g⁻¹ = _
    rw [Subgroup.conjBy_conjBy, inv_mul_cancel, Subgroup.conjBy_one]] at hfirst
  rw [first_eq_zpowers] at hfirst
  obtain ⟨h, hh⟩ := isConj_iff.mp (isConj_swap (by decide : (0 : Fin 7) ≠ 1) hab)
  have hlast := hP.2.2.1 _ hfirst h
  rw [MonoidHom.map_zpowers] at hlast
  exact (show (MulAut.conj h) (swap 0 1) = swap a b from hh) ▸ hlast

/-- In the canonical Sylow coordinates the family generates D. -/
theorem generatedBy_eq_threeTranspositions {P : Set (Subgroup (Perm (Fin 7)))}
    (hP : IsStable (BinaryPermutation.naturalRepresentation (Fin 7)) P) (R : Subgroup (Perm (Fin 7)))
    (hR : IsPGroup 2 R) (hD : D 7 ≤ R) :
    generatedBy P R = threeTranspositions := by
  rw [← D_eq_threeTranspositions]
  apply le_antisymm
  · apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA, hAR⟩
    exact Odd.caseAFamily_le_D_of_isPGroup (Or.inr rfl) hR hD
      ((Odd.isBestOffender_natural_iff_caseAFamily (Or.inr rfl) A).mp (hP.2.1 A hA)) hAR
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

/-- The unique-offender premise of B.2.20 is not available in these canonical
coordinates: the rank-one and rank-three groups are distinct best offenders. -/
theorem exists_distinct_offenders (R : Subgroup (Perm (Fin 7))) (hD : D 7 ≤ R) :
    ∃ A B : Subgroup (Perm (Fin 7)), A ≤ R ∧ B ≤ R ∧
      IsBestOffender (BinaryPermutation.naturalRepresentation (Fin 7)) A ∧
      IsBestOffender (BinaryPermutation.naturalRepresentation (Fin 7)) B ∧ A ≠ B := by
  refine ⟨disjointTranspositions 7 1, D 7,
    (disjointTranspositions_mono (by decide : 1 ≤ 7 / 2)).trans hD, hD,
    (Odd.isBestOffender_disjointTranspositions (Or.inr rfl) (by decide) (by decide)).2.2.2,
    (Odd.isBestOffender_disjointTranspositions (Or.inr rfl) (by decide) (by decide)).2.2.2, ?_⟩
  intro he
  have hr := congrArg rank he
  rw [Odd.rank_disjointTranspositions (Or.inr rfl) (by decide),
    Odd.rank_disjointTranspositions (Or.inr rfl) (by decide)] at hr
  norm_num at hr

/-- Conjugating the ambient Sylow conjugates its generated stable-family subgroup. -/
theorem generatedBy_conj {P : Set (Subgroup (Perm (Fin 7)))}
    (hP : IsStable (BinaryPermutation.naturalRepresentation (Fin 7)) P) (R : Subgroup (Perm (Fin 7))) (g : Perm (Fin 7)) :
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
      change A.conjBy g⁻¹ ≤ (R.conjBy g).conjBy g⁻¹ at hm
      change A.conjBy g⁻¹ ≤ R
      simpa only [Subgroup.conjBy_conjBy, inv_mul_cancel, Subgroup.conjBy_one] using hm
    have hi : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ generatedBy P R :=
      le_iSup_of_le _ (le_iSup_of_le ⟨hback, hle⟩ le_rfl)
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hi
    change (A.conjBy g⁻¹).conjBy g ≤ _ at hm
    simpa only [Subgroup.conjBy_conjBy, mul_inv_cancel, Subgroup.conjBy_one] using hm

/-- Every Sylow marking is simultaneously conjugate to the three chosen swaps. -/
theorem exists_generatedBy_marking {P : Set (Subgroup (Perm (Fin 7)))}
    (hP : IsStable (BinaryPermutation.naturalRepresentation (Fin 7)) P) (R : Sylow 2 (Perm (Fin 7))) :
    ∃ g : Perm (Fin 7),
      (generatedBy P (R : Subgroup _)).map (MulAut.conj g).toMonoidHom = threeTranspositions := by
  obtain ⟨Q, hDQ, _⟩ := Odd.exists_sylow_containing_D (Or.inr rfl : 7 = 5 ∨ 7 = 7)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 7)) R Q
  refine ⟨g, ?_⟩
  rw [generatedBy_conj hP]
  have he : (R : Subgroup _).map (MulAut.conj g).toMonoidHom = Q := by
    rw [← hg]
    rfl
  rw [he]
  exact generatedBy_eq_threeTranspositions hP Q Q.isPGroup' hDQ

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking
end
