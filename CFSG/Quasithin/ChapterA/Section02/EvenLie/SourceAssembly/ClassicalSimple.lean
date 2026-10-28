module

public import CFSG.Quasithin.ChapterA.Section02.EvenLie.Models
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.UnitaryRanks
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import Theory.SpecificGroups.ClassicalUnitary.TheoremDRootNormalizer
public import Theory.SpecificGroups.ClassicalUnitary.TheoremDRootNormalizer.BinaryForms

/-!
# The linear and unitary Case I branches of A.2.18

The actual root two-local normalizers bound the linear degree and unitary
dimension. The binary linear Levi excludes degree six and higher. In dimension
five the actual unitary line parabolic forces fixed-field order four. Ordinary
odd-prime ranks exclude U4 and U5(4) from C while retaining them in B.

These source conclusions need no quotient inheritance of quasithinness and
no assumption about a family classification. The input ranges are those of
the complete known-simple catalogue, including the unitary dimension-two alias.
Source: Aschbacher--Smith A.2.18, printed p.40.
-/

public section
open CFSG.KnownSimple CFSG.Quasithin.ClassificationModels BenderSuzuki.MatrixGroups
open HermitianForm.IdentityGram Theory.SpecificGroups.UnitaryRootNormalizer
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The full characteristic-two linear family supplies both source lists. -/
theorem caseI_linear (hG : IsQuasithin G) {d a : ℕ} (ha : 0 < a)
    (hp : LinearParameters d (2 ^ a)) (iso : ClassicalGroup.IsPSL G d (2 ^ a)) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  have hc : IsTheoremCModel G := by
    obtain hsmall | ⟨ha1, hd⟩ := linear_parameters hG ha iso
    · have hcases : d = 2 ∨ d = 3 := by have := hp.2.1; omega
      rcases hcases with rfl | rfl
      · have ha2 : 2 ≤ a := by
          by_contra hn
          have : a = 1 := by omega
          have hh := hp.2.2 rfl
          simp [this] at hh
        exact .bender (.linear a ha2 iso)
      · exact .rank_two a (.linear ha iso)
    · by_cases hsmall : d ≤ 3
      · have hcases : d = 2 ∨ d = 3 := by have := hp.2.1; omega
        rcases hcases with rfl | rfl
        · have hh := hp.2.2 rfl
          simp [ha1] at hh
        · exact .rank_two a (.linear ha iso)
      · exact .linear_binary d (by omega) (by simpa [ha1] using iso)
  exact ⟨hc.toTheoremBModel, fun _ => hc⟩

private theorem unitary_degree_le_five (hG : IsQuasithin G)
    {d a : ℕ} (ha : 0 < a) (iso : ClassicalGroup.IsPSU G d (2 ^ a)) : d ≤ 5 := by
  by_contra hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 6 ≤ d by omega)
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := iso
  let : CharP F 2 := charP_binary ha hcard
  obtain ⟨C, hC⟩ := exists_binary_identity_basis J ha hcard hconj
  let ep := e.trans (projectiveEquiv J C hC)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup (identityGram J)) :=
    Finite.of_injective ep.symm ep.symm.injective
  exact not_quasithin k (identityGram J) rfl hcard
    (Nat.one_lt_pow (by omega) (by decide))
    (even_two.pow_of_ne_zero (by omega)) hconj
    (Theory.GroupTheory.isQuasithin_of_equiv ep hG)

omit [Finite G] in
private theorem unitary_two_linear {a : ℕ} (ha : 0 < a)
    (iso : ClassicalGroup.IsPSU G 2 (2 ^ a)) : ClassicalGroup.IsPSL G 2 (2 ^ a) := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := iso
  let : CharP F 2 := charP_binary ha hcard
  have hc := fixed_card_binary J ha hcard hconj
  obtain ⟨ep⟩ := nonempty_projectiveTwoEquiv J hcard hc
  exact ⟨FixedBy.subfield F J.conj, inferInstance, inferInstance, hc, ⟨e.trans ep⟩⟩

private theorem unitary_five_exponent (hG : IsQuasithin G) {a : ℕ} (ha : 0 < a)
    (iso : ClassicalGroup.IsPSU G 5 (2 ^ a)) : a = 2 := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := iso
  let : CharP F 2 := charP_binary ha hcard
  obtain ⟨C, hC⟩ := exists_binary_identity_basis J ha hcard hconj
  let ep := e.trans (projectiveEquiv J C hC)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup (identityGram J)) :=
    Finite.of_injective ep.symm ep.symm.injective
  have hq4 := unitary_five_field_size_eq_four_of_quasithin_identity
    (identityGram J) rfl hcard (even_two.pow_of_ne_zero (by omega))
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) ha) hconj
    (Theory.GroupTheory.isQuasithin_of_equiv ep hG)
  exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ))) hq4

/-- The full characteristic-two unitary family, with the B/C distinction retained. -/
theorem caseI_unitary (hG : IsQuasithin G) {d a : ℕ} (ha : 0 < a)
    (hp : UnitaryParameters d (2 ^ a)) (iso : ClassicalGroup.IsPSU G d (2 ^ a)) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  have hd := unitary_degree_le_five hG ha iso
  have hmin := hp.2.1
  interval_cases d
  · exact caseI_linear hG ha ⟨hp.1, by decide, hp.2.2.1⟩
      (unitary_two_linear ha iso)
  · have ha2 : 2 ≤ a := by
      by_contra hn
      have : a = 1 := by omega
      exact hp.2.2.2 rfl (by simp [this])
    have hc : IsTheoremCModel G := .bender (.unitary a ha2 iso)
    exact ⟨hc.toTheoremBModel, fun _ => hc⟩
  · refine ⟨.rank_two a (.unitary_four ha iso), ?_⟩
    intro hstrong
    obtain ⟨p, hprime, hodd, hr⟩ := unitary_four_exists_odd_rank_gt_two hp.1
      (even_two.pow_of_ne_zero (by omega)) iso
    exact (not_lt_of_ge (hstrong p hprime hodd) hr).elim
  · have ha2 := unitary_five_exponent hG ha iso
    refine ⟨.rank_two a (.unitary_five ha2 iso), ?_⟩
    intro hstrong
    have hr := unitary_five_four_ordinary_rank_gt_two (by simpa [ha2] using iso)
    exact (not_lt_of_ge (hstrong 5 (by decide) (by decide)) hr).elim

end CFSG.Quasithin.ChapterA.Section02.EvenLie
