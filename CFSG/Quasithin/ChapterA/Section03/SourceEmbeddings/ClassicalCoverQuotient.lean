module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.SpecificGroups.SU3.FixedFieldTwo

/-!
# Central quotients of the classical three-cover rows

The literal central quotient of SL₃ or SU₃ is identified with its projective
carrier. The cover parameter selects an odd-field Theorem C model, a binary
unitary Bender model, or a binary linear-three model. The solvable PSU₃(2)
endpoint is incompatible with perfection of the original cover.

Source: Aschbacher–Smith A.3.6(2), printed pp.43–45. This adapter retains
the actual center quotient required by the exceptional A.3.12 application.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ClassicalCoverQuotient
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G]

private def center_quotient_equiv {H : Type*} [Group H] (e : G ≃* H) :
    (G ⧸ center G) ≃* (H ⧸ center H) :=
  QuotientGroup.congr (center G) (center H) e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

private theorem unitary_central_quotient {F : Type} [Field F] [Finite F]
    (J : HermitianForm 3 F) {q : ℕ} (hq : 2 < q)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    (hfixed : Nat.card {x : F // J.conj x = x} = q)
    (e : G ≃* J.specialSubgroup) : ClassicalGroup.IsPSU (G ⧸ center G) 3 q := by
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J q hq hcard hfixed
  let := J.projective_isPerfect_of_fixed_card hq hcard hfixed
  have hz : center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ :=
    (inferInstance : (center (ProjectiveSpecialUnitaryMatrixGroup J)).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht))
  let a : (J.specialSubgroup ⧸ center J.specialSubgroup) ≃*
      ProjectiveSpecialUnitaryMatrixGroup J :=
    (QuotientGroup.quotientMulEquivOfEq (J.specialToProjective_ker_eq_center hz).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective J.specialToProjective_surjective)
  exact ⟨F,inferInstance,inferInstance,J,hcard,hconj,⟨(center_quotient_equiv e).trans a⟩⟩

private theorem not_unitary_two [Group.IsPerfect G] (h : IsSU G 3 2) : False := by
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := h
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Group.IsPerfect.ofSurjective (f := J.specialToProjective.comp e.toMonoidHom)
      (J.specialToProjective_surjective.comp e.surjective)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let : Nontrivial (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [HermitianForm.FixedFieldTwo.card_projective J hcard hconj]
      norm_num)
  exact Group.IsPerfect.not_isSolvable _
    (HermitianForm.FixedFieldTwo.projective_isSolvable J hcard hconj)

/-- The actual central quotient of each classical three-cover row. -/
theorem models [Group.IsPerfect G]
    (unitary : Bool) (q : ℕ) (hq : CoverParameter unitary q) (hm : IsSLSign G unitary 3 q) :
    ChapterA.Section02.IsTheoremCOddModel (G ⧸ center G) ∨
      ClassificationModels.IsBenderModel (G ⧸ center G) ∨
      ∃ n, 1 ≤ n ∧ ClassicalGroup.IsPSL (G ⧸ center G) 3 (2 ^ n) := by
  cases unitary with
  | false =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have hp : ClassicalGroup.IsPSL (G ⧸ center G) 3 q :=
      ⟨F,inferInstance,inferInstance,hF,⟨center_quotient_equiv e⟩⟩
    rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hprime,hodd⟩
    · exact Or.inr (Or.inr ⟨n,hn,hp⟩)
    · exact Or.inl (.linear_three q hprime hodd hp)
  | true =>
    change IsSU G 3 q at hm
    rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hprime,hodd⟩
    · have hn2 : 2 ≤ n := by
        by_contra h
        have he : n = 1 := by omega
        subst n
        exact not_unitary_two (by simpa using hm)
      obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
      have hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ n :=
        FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hF hconj
      have hlarge : 2 < 2 ^ n := by
        have := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn2
        norm_num at this
        omega
      exact Or.inr (Or.inl (.unitary n hn2
        (unitary_central_quotient J hlarge hF hconj hfixed e)))
    · have hp2 : 2 < q := by
        have := hprime.two_le
        have : q ≠ 2 := by rintro rfl; norm_num at hodd
        omega
      obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
      let : Fact q.Prime := ⟨hprime⟩
      have hfixed : Nat.card {x : F // J.conj x = x} = q := by
        simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
          J.conj q 1 (by decide) (by simpa using hF) (by simpa using hconj)
      exact Or.inl (.unitary_three q hprime hodd
        (unitary_central_quotient J hp2 hF hconj hfixed e))

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ClassicalCoverQuotient
