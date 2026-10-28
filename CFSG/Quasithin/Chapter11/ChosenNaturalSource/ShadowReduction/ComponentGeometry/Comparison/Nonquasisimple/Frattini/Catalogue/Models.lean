module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Statements
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.SpecificGroups.G2.TwoRankLower
public import Theory.SpecificGroups.ReeF4.TwoRankLower
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock
public import Theory.SpecificGroups.Triality.StandardTwoRank
public import Theory.Mathieu.TwoRankLower
public import Theory.SpecificGroups.Janko1.TwoRank
public import Theory.SpecificGroups.Janko4.TwoRankLower
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.TwoRankLower
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.TwoRankLower
public import Theory.SpecificGroups.Rudvalis.TwoRankLower
public import BenderSuzuki.External.Huppert.II.theorem_10_13
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# The complete 11.1.1 catalogue at two-rank one

A nonquasisimple SQTK C-component modulo its two-core has two-rank at
most one. This excludes all the exceptional Lie and sporadic rows using
concrete elementary subgroups already constructed in the carrier modules.
The classical rows use their actual linear or unitary quotient maps;
perfectness of a unitary central cover is inherited from the original
component. Both central three-cover rows retain their quasisimplicity.

Thus the full field-four list leaves just the nilpotent SL₂(5) extension
and the exceptional elementary-plane extension of SL₂(p). No simplicity
or order certificate for J₄ or Rudvalis is needed for this reduction.
The chosen-flag application is in the parent Catalogue module.

Source: Aschbacher--Smith, 11.1.1, printed p.761, and the opening
nonquasisimple paragraph of 11.4.2, printed p.777; A.3.6 supplies the
noncentral-Fitting two-rank bound used by that application.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini.Catalogue
open Chapter1.Section02.LocalModels LocalGeometry.Components
variable {A : Type*} [Group A]

private theorem quasi_of_simple [IsSimpleGroup A] [Group.IsPerfect A] : IsQuasisimple A := by
  have hz : center A = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center A) inferInstance).resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp he))
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩

private theorem quasi_psl [Group.IsPerfect A] {q : ℕ} (hq : 3 < q)
    (h : ClassicalGroup.IsPSL A 2 q) : IsQuasisimple A := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup A := e.isSimpleGroup
  exact quasi_of_simple

private theorem psu_five_simple {F : Type*} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5) :
    IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 5 1 (by decide)
    (by simpa using hc) (by simpa using hconj)
  exact BenderSuzuki.External.huppert_II_10_13 J 5 (by decide) hc (by simpa using hf)

private theorem quasi_three [Group.IsPerfect A] (u : Bool)
    (h : IsPSLSign A u 3 5 ∨ IsSLSign A u 3 5) : IsQuasisimple A := by
  cases u with
  | false =>
    rcases h with h | h
    · obtain ⟨F, _, _, _, ⟨e⟩⟩ := h
      exact IsQuasisimple.of_mulEquiv e.symm
    · obtain ⟨F, _, _, _, ⟨e⟩⟩ := h
      exact IsQuasisimple.of_mulEquiv e.symm
  | true =>
    rcases h with h | h
    · obtain ⟨F, _, _, J, hc, hconj, ⟨e⟩⟩ := h
      let := psu_five_simple J hc hconj
      let : IsSimpleGroup A := e.isSimpleGroup
      exact quasi_of_simple
    · obtain ⟨F, _, _, J, hc, hconj, ⟨e⟩⟩ := h
      let : Group.IsPerfect J.specialSubgroup := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      let := psu_five_simple J hc hconj
      let : Group.IsPerfect (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
        Group.IsPerfect.ofSurjective J.specialToProjective_surjective
      let := quasi_of_simple (A := BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
      let cov : PerfectCentralCovering.Cover J.specialSubgroup
          (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) := {
        toMonoidHom := J.specialToProjective
        surjective := J.specialToProjective_surjective
        isPerfect := inferInstance
        ker_le_center := J.specialToProjective_ker_le_center }
      let := cov.isQuasisimple
      exact IsQuasisimple.of_mulEquiv e.symm

variable [Finite A]

/-- Every characteristic-two row is quasisimple or has two-rank greater than one. -/
theorem lie_quasisimple_of_rank_le_one {n : ℕ} (hn : 0 < n)
    (hr : primeRank 2 A ≤ 1) (h : LieOvergroup A n) : IsQuasisimple A := by
  cases h with
  | sl3 hm =>
    obtain ⟨F, _, _, _, ⟨e⟩⟩ := hm
    exact IsQuasisimple.of_mulEquiv e.symm
  | psl3 hm =>
    obtain ⟨F, _, _, _, ⟨e⟩⟩ := hm
    exact IsQuasisimple.of_mulEquiv e.symm
  | sp4 hm =>
    obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hm
    rw [primeRank_equiv 2 e,
      Theory.SpecificGroups.SymplecticFour.EvenTwoRank.rank hc hn] at hr
    omega
  | g2 hm =>
    obtain ⟨F, _, _, _, ⟨e⟩⟩ := hm
    have hb := Atlas.G2.three_le_primeRank_two F
    rw [primeRank_equiv 2 e] at hr
    omega
  | ree m _ _ hm =>
    obtain ⟨d, ⟨e⟩⟩ := hm
    have hb := ReeF4.three_le_twoRank m
    rw [primeRank_equiv 2 (e.trans d.modelEquiv)] at hr
    omega
  | triality hm =>
    have hb := Triality.Standard.TwoRank.derived_twoRank_ge_three_mul_of_model n hn hm
    have hi := primeRank_le_of_injective 2 (commutator A).subtype Subtype.val_injective
    omega
  | trialityCube m hm _ hmodel =>
    have hb := Triality.Standard.TwoRank.derived_twoRank_ge_three_mul_of_model m hm hmodel
    have hi := primeRank_le_of_injective 2 (commutator A).subtype Subtype.val_injective
    omega

/-- The full field-four list leaves exactly its two genuine extension rows. -/
theorem fieldFour_extensions [Group.IsPerfect A] (hr : primeRank 2 A ≤ 1)
    (hn : ¬ IsQuasisimple A) (h : FieldFourOvergroup A) :
    HasExtension A (fun P _ => Group.IsNilpotent P ∧ Odd (Nat.card P))
      (fun Q _ => Source.IsSL Q 2 5) ∨
    ∃ p, Source.ExceptionalPrime p ∧
      HasExtension A (ElementaryModel p 2) (fun Q _ => Source.IsSL Q 2 p) := by
  cases h with
  | alternating hm =>
    obtain ⟨e⟩ := hm
    let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup A := e.isSimpleGroup
    exact (hn quasi_of_simple).elim
  | alternatingCover hm => exact (hn hm.1).elim
  | primeLinear p hp hm =>
    have hp3 : 3 < p := by have := hp.1.two_le; have := hp.2.1; omega
    exact (hn (quasi_psl hp3 hm)).elim
  | linearTwentyFive hm => exact (hn (quasi_psl (by decide) hm)).elim
  | three u hm => exact (hn (quasi_three u hm)).elim
  | m22 hm =>
    rw [primeRank_equiv 2 hm.some] at hr
    have := Sporadic.Mathieu.m22_four_le_twoRank
    omega
  | m22Cover hm => exact (hn hm.1).elim
  | m23 hm =>
    rw [primeRank_equiv 2 hm.some] at hr
    have := Sporadic.Mathieu.m23_four_le_twoRank
    omega
  | j1 hm =>
    rw [primeRank_equiv 2 hm.some] at hr
    have := Janko1.three_le_twoRank
    omega
  | j2 hm =>
    rw [primeRank_equiv 2 hm.some] at hr
    have := Sporadic.LeechRelated.J2.TwoRank.three_le_twoRank
    omega
  | j4 hm =>
    rw [primeRank_equiv 2 hm.some] at hr
    have := Janko4.eleven_le_twoRank
    omega
  | hs hm =>
    rw [primeRank_equiv 2 hm.some] at hr
    have := Sporadic.LeechRelated.HS.three_le_twoRank
    omega
  | ru hm =>
    rw [primeRank_equiv 2 hm.some] at hr
    have := Rudvalis.three_le_twoRank
    omega
  | nilpotentExtension hm => exact Or.inl hm
  | elementaryExtension p hp hm => exact Or.inr ⟨p, hp, hm⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini.Catalogue
