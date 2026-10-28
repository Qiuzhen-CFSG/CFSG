module
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremC

/-!
# Completed outer-solvability branches of the Theorem B model list

The full Theorem C inspection supplies its shared rows. Actual alternating
conjugation handles all alternating degrees, including the additional B row
A₉, and inner–diagonal–field coverage handles PSL₂ over every odd finite field.
The inherited nonabelian simple hypothesis rules out small solvable carriers.

These are proved branches for the full Theorem B assembly; the other B-only
classical and sporadic rows remain separate mathematical obligations.
Source: Aschbacher–Smith A.2.2–4, printed p.33, and 4.4.3, printed p.621.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceComponents.TheoremBOuter

variable {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]

omit [Finite S] in
private theorem perfect (hna : ¬ IsMulCommutative S) : Group.IsPerfect S := by
  refine ⟨(Subgroup.Normal.eq_bot_or_eq_top (H := commutator S) inferInstance).resolve_left ?_⟩
  intro hbot
  exact hna ((commutator_eq_bot_iff S).mp hbot)

theorem of_theoremC (hna : ¬ IsMulCommutative S)
    (hS : Section02.IsTheoremCModel S) : Group.IsSolvable (MulAut.Outer S) := by
  let : Group.IsPerfect S := perfect hna
  exact (source_model_outer_isSolvable_even
    (fun hRu => @Chapter1.XiEmbedding.OuterModels.rudvalis_outer_isSolvable_of_involution_fibers hRu)
    hna hS).1

omit [Finite S] in
theorem alternating (hna : ¬ IsMulCommutative S) {n : ℕ}
    (iso : Nonempty (S ≃* alternatingGroup (Fin n))) :
    Group.IsSolvable (MulAut.Outer S) := by
  obtain ⟨e⟩ := iso
  have hn : 5 ≤ n := by
    by_contra! hn
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm (Fin n)) :=
      Group.isSolvable_of_isSolvable_injective
        (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by omega : n ≤ 4)))
    let : Group.IsSolvable (alternatingGroup (Fin n)) := inferInstance
    let : Group.IsSolvable S := Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    let : Group.IsPerfect S := perfect hna
    exact Group.IsPerfect.not_isSolvable S inferInstance
  by_cases h6 : n = 6
  · subst n
    let := AlternatingSix.ShadowLocal.outer_isSolvable
    exact MulAut.isSolvable_outer_of_mulEquiv e
  let A := alternatingGroup (Fin n)
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hc : Nat.card (Equiv.Perm (Fin n) ⧸ A) = 2 ^ 1 := by
    rw [← A.index_eq_card]
    exact alternatingGroup.index_eq_two
  let : Group.IsNilpotent (Equiv.Perm (Fin n) ⧸ A) := (IsPGroup.of_card hc).isNilpotent
  let : Group.IsSolvable (MulAut.Outer A) := by
    apply Group.isSolvable_of_surjective (f := MulAut.outerAction A)
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
    obtain ⟨s, rfl⟩ :=
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn h6).surjective a
    exact ⟨QuotientGroup.mk' A s, rfl⟩
  exact MulAut.isSolvable_outer_of_mulEquiv e

omit [Finite S] in
theorem linear_two_odd (hna : ¬ IsMulCommutative S) {q : ℕ} (ho : Odd q)
    (hS : ClassicalGroup.IsPSL S 2 q) : Group.IsSolvable (MulAut.Outer S) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hS
  let : Fintype F := Fintype.ofFinite F
  let : Group.IsPerfect S := perfect hna
  let : Group.IsPerfect PSL(2,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hcard : 3 < Nat.card F := by
    by_contra! hsmall
    have hgt : 1 < Nat.card F := Finite.one_lt_card
    have hodd : Odd (Nat.card F) := hF.symm ▸ ho
    obtain ⟨k,hk⟩ := hodd
    have hthree : Nat.card F = 3 := by omega
    exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three hthree inferInstance
  have hchar : ringChar F ≠ 2 := by
    intro hc
    have hEven := (FiniteField.even_card_iff_char_two (F := F)).mp hc
    rw [← Nat.card_eq_fintype_card, hF] at hEven
    obtain ⟨k,hk⟩ := ho
    omega
  let := Theory.PSL2.OuterSolvable.outer_isSolvable_of_semilinear_coverage
    (Theory.PSL2.OuterSolvable.odd_semilinear_coverage hchar hcard)
  exact MulAut.isSolvable_outer_of_mulEquiv e
end CFSG.Quasithin.ChapterA.Section03.SourceComponents.TheoremBOuter
