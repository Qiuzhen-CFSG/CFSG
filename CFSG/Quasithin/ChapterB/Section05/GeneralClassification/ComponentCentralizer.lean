module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentCenters
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.RankOneComparison
public import Theory.GroupTheory.PrimeRankZero
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.SpecificGroups.BinaryLinear.SylowCenters
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Selecting the quasisimple FF row by its component centralizer

Every product alternative in B.5.6 has a cubic subgroup in each factor.
An ordinary component lies in one factor, so the other contributes a cubic
subgroup to its centralizer. In the outer A₆–C₃ alternative the component is
the literal A₆ factor and the C₃ factor centralizes it. Consequently a
three-free component centralizer selects the full quasisimple alternative.

Source: Aschbacher--Smith B.5.6, printed p.105, applied in12.6.11, p.825.
-/

public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.ChapterB.SourceInduction
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

omit [Finite D] in
private theorem component_le_factor {A B C : Subgroup D}
    (h : InternalProduct A B) (hC : IsComponent D C) : C ≤ A ∨ C ≤ B := by
  let := h.swap.second_normal
  let := h.second_normal
  rcases hC.normal_dichotomy A with ha | ha
  · exact Or.inl ha
  rcases hC.normal_dichotomy B with hb | hb
  · exact Or.inr hb
  have hc : C ≤ centralizer ((A ⊔ B : Subgroup D) : Set D) := by
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp ha))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb))
  rw [h.sup_eq_top] at hc
  have hcc : ⁅C,C⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hc.trans (centralizer_le (show (C : Set D) ⊆ (⊤ : Subgroup D) from Set.subset_univ _)))
  let := hC.2
  rw [commutator_eq_self] at hcc
  exact (hC.isCComponent.ne_bot hcc).elim

private theorem product_centralizer_three_rank_pos {A B C : Subgroup D}
    (h : InternalProduct A B) (hC : IsComponent D C)
    (hA : 0 < primeRank 3 A) (hB : 0 < primeRank 3 B) :
    0 < primeRank 3 (centralizer (C : Set D)) := by
  rcases component_le_factor h hC with ha | hb
  · have hc : B ≤ centralizer (C : Set D) :=
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h.commutator_eq_bot)).trans
        (centralizer_le ha)
    exact hB.trans_le (primeRank_le_of_injective 3 (inclusion hc) (inclusion_injective hc))
  · have hc : A ≤ centralizer (C : Set D) :=
      (commutator_eq_bot_iff_le_centralizer.mp h.commutator_eq_bot).trans
        (centralizer_le hb)
    exact hA.trans_le (primeRank_le_of_injective 3 (inclusion hc) (inclusion_injective hc))

/-- The original component is the whole generalized Fitting subgroup;
all B.5.1 clauses survive the row selection. -/
theorem AdequateAlternative.quasisimple_of_component_three_free_centralizer
    (h : AdequateAlternative ρ) {C : Subgroup D} (hC : IsComponent D C)
    (hc : Nat.Coprime 3 (Nat.card (centralizer (C : Set D)))) :
    generalizedFitting D = C ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ C) := by
  have hz : primeRank 3 (centralizer (C : Set D)) = 0 :=
    PrimeRank.eq_zero_iff_not_dvd_card.mpr (Nat.prime_three.coprime_iff_not_dvd.mp hc)
  let : Nontrivial C := (nontrivial_iff_ne_bot C).mpr hC.isCComponent.ne_bot
  let : Nontrivial D := Function.Injective.nontrivial C.subtype_injective
  cases h.of_nontrivial ρ with
  | quasisimple hq ha =>
    have he : generalizedFitting D = C := (hC.eq_of_le
      ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal,hq⟩
      (component_le_generalizedFitting D C hC)).symm
    exact ⟨he,he ▸ ⟨ha⟩⟩
  | symmetricThree d =>
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
      apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
      (f := d.equiv.toMonoidHom) d.equiv.injective
    let := hC.2
    exact (Group.IsPerfect.not_isSolvable C inferInstance).elim
  | twoFactors d =>
    have hp := product_centralizer_three_rank_pos d.product hC
      d.firstCase.three_rank_pos d.secondCase.three_rank_pos
    omega
  | outerSixThree d =>
    let := hC.2
    let := d.first_normal
    let := d.quotient_first_solvable
    have he : C = d.first := hC.eq_of_le d.first_isComponent
      (le_of_isPerfect_of_solvable_quotient C d.first)
    have hle : d.second ≤ centralizer (C : Set D) := by
      rw [he]
      intro b hb
      exact mem_centralizer_iff.mpr (fun a ha => d.first_second_commute ⟨a,ha⟩ ⟨b,hb⟩)
    have h3 : 3 ∣ Nat.card d.second := by
      rw [Nat.card_congr d.secondEquiv.toEquiv]
      simp
    have hp : 0 < primeRank 3 d.second := Nat.pos_of_ne_zero
      (fun hh => PrimeRank.eq_zero_iff_not_dvd_card.mp hh h3)
    have hb := primeRank_le_of_injective 3 (inclusion hle) (inclusion_injective hle)
    omega
  | hyperplane d =>
    have hA : 0 < primeRank 3 d.first := by
      have h3 := Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
        (F := ZMod 2) (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide)
      have hd := (h3.trans (card_subgroup_dvd_card _)).trans
        (Subgroup.card_dvd_of_surjective (QuotientGroup.mk' (center
          (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))) (QuotientGroup.mk'_surjective _))
      rw [←Nat.card_congr d.firstEquiv.toEquiv] at hd
      exact Nat.pos_of_ne_zero (fun hh => PrimeRank.eq_zero_iff_not_dvd_card.mp hh hd)
    have hp := product_centralizer_three_rank_pos d.product hC hA d.secondCase.three_rank_pos
    omega
end CFSG.Quasithin.ChapterB.SourceInduction

public section
open scoped MatrixGroups
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
private theorem linear_three_card_ne_360 (F : BinaryField) :
    Nat.card SL(3,F.Carrier) ≠ 360 := by
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
  have hq : 2 ≤ Nat.card F.Carrier := Finite.one_lt_card
  by_cases he : Nat.card F.Carrier = 2
  · simp [he]
  · have hq3 : 3 ≤ Nat.card F.Carrier := by omega
    have hb : 5616 ≤ Nat.card F.Carrier ^ 3 * (Nat.card F.Carrier ^ 3 - 1) *
        (Nat.card F.Carrier ^ 2 - 1) := by
      calc
        5616 = 3^3 * (3^3-1) * (3^2-1) := by norm_num
        _ ≤ _ := by gcongr
    omega
private theorem binary_card (n : ℕ) :
    Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp
private theorem binary_higher_card_ne_360 {d : ℕ} (hd : d = 4 ∨ d = 5) :
    Nat.card SL(d,ZMod 2) ≠ 360 := by
  rcases hd with rfl | rfl <;> rw [binary_card] <;> norm_num [Fin.prod_univ_succ]

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {C : Subgroup D}
/-- At the actual A₆ component order, none of the reducible B.5.1 rows is possible. -/
theorem ProjectiveLine.QuasisimpleSourceConclusion.card360_moved_irrPlus
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ C) (hc : Nat.card C = 360) :
    IsIrrPlus ρ C (subspaceCommutator ρ ⊤ C) := by
  cases c.clause_one with
  | irreducible hi _ _ _ _ =>
    rwa [c.sectionData.space_eq] at hi
  | doubleThree F _ e _ _ =>
    exact (linear_three_card_ne_360 F ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
  | naturalDual d hd _ hn =>
    obtain ⟨e⟩ := hn
    exact (binary_higher_card_ne_360 hd ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨e⟩ := hn
    exact (binary_higher_card_ne_360 hd ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
end CFSG.Quasithin.ChapterB.SourceInduction
